import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0866 : checkSingleBlackFast2 (-9, 3) 18839 .west (-19, -11) (-10, -31) = true := by
  decide +kernel

end LangtonsAnt
