import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0712 : checkSingleBlackFast (4, -11) 21901 .west (-12, 2) (-36, -5) = true := by
  decide +kernel

end LangtonsAnt
