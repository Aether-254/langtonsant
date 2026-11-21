import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0170 : checkSingleBlackFast (-6, 8) 4528 .north (-1, -3) (-17, -5) = true := by
  decide +kernel

end LangtonsAnt
