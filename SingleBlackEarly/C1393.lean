import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1393 : checkSingleBlackFast2 (-16, 3) 15807 .east (-2, -5) (-24, -28) = true := by
  decide +kernel

end LangtonsAnt
