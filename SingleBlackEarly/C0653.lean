import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0653 : checkSingleBlackFast (9, -12) 13939 .west (-9, 0) (-21, -21) = true := by
  decide +kernel

end LangtonsAnt
