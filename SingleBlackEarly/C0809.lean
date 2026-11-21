import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0809 : checkSingleBlackFast (24, -4) 9808 .north (-6, 7) (0, -21) = true := by
  decide +kernel

end LangtonsAnt
