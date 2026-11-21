import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1972 : checkSingleBlackFast2 (-72, -44) 17721 .west (29, 35) (-55, 12) = true := by
  decide +kernel

end LangtonsAnt
