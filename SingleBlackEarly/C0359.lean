import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0359 : checkSingleBlackFast (12, 0) 10247 .west (-7, -3) (-22, -17) = true := by
  decide +kernel

end LangtonsAnt
