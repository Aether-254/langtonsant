import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0591 : checkSingleBlackFast (20, 13) 7368 .north (-9, 7) (-1, -19) = true := by
  decide +kernel

end LangtonsAnt
