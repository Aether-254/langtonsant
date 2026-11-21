import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0566 : checkSingleBlackFast (19, -3) 4509 .west (-12, 1) (-15, -13) = true := by
  decide +kernel

end LangtonsAnt
