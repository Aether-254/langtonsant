import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2203 : checkSingleBlackFast2 (-93, -69) 16135 .west (33, 44) (-63, 25) = true := by
  decide +kernel

end LangtonsAnt
