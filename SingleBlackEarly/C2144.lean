import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2144 : checkSingleBlackFast2 (-84, -64) 17276 .north (37, 27) (-63, -43) = true := by
  decide +kernel

end LangtonsAnt
